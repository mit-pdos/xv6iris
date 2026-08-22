(* ProofSysWrite.v -- whole-function WP for sys_write(), the third syscall
   shell over the B2-converted file.c contracts (fs-sysfile S4d).

     uint64 sys_write(void) {
       struct file *f;
       int n;
       uint64 p;
       argaddr(1, &p);
       argint(2, &n);
       if (argfd(0, 0, &f) < 0) return -1;
       return filewrite(f, p, n);
     }

   Twenty-five instructions; CodeSysWrite.v has the listing and SpecSysWrite.v
   the shape notes.  THE OBJECT CODE IS SYS_READ'S, INSTRUCTION FOR
   INSTRUCTION, so ProofSysRead.v is this file's line-for-line twin: only the
   three [jal] targets differ (argaddr, argint, filewrite), and only the third
   differs in kind.  ProofSysFstat.v is the template both descend from -- the
   B1 seam ([ProcInv.proc_priv_lend] at the descriptor argfd resolved,
   [proc_priv_core] down to the file.c callee, [proc_ofiles_repay] +
   [proc_priv_join] on the way back, with the [upd_upt] crossing free by
   [cbn]) is verbatim.  THREE THINGS DIFFER FROM sys_fstat:

   * A SIX-SLOT FRAME.  [c.addi16sp sp,sp,-48] ([KernelRvcDecode.stk_push_48])
     rather than sys_fstat's [c.addi sp,-32], and there is no
     [stack_own_6_elim] -- the frame is peeled and rebundled with
     ProofSysPipe's [rewrite stack_own_slots; cbn [seq]] recipe, which works
     at any width.

   * THE [int n] IS THE UPPER WORD OF SLOT 4.  [&n] is [s0-28] and the slot
     base [s0-32], so [InstrBytes.word_pointsto_split4] carves the slot in
     two before argint is called and [word_pointsto_join4] puts it back for
     the epilogue's [c.addi16sp].  The 8-alignment fact has to come out with
     [word_pointsto_aligned_p] BEFORE the split (the halves no longer carry
     it).  sys_close and sys_sbrk make the same move.

   * ONE EXTRA CALLEE, argint.  It hands back [ip ↦₄ arg_int32 v2], the
     [c.sw] narrowing; the [lw] at +0x30 then reads it back SIGNED, so what
     reaches filewrite's a2 is [sign_extend' 64 (trunc32 v2)], which
     [SpecSysRead.sys_rw_count_reg] says is [mword_of_int (sys_rw_count v2)]
     exactly.  That is the whole numeric story, and the write side owes LESS
     of it than the read side: only [0 <= n] stays a premise of this shell
     (filewrite's chunking closes writei's joint bound internally, so
     fileread's MAXFILE row is absent), and the upper half [n < 2^31] is free
     for a sign-extended 32-bit cell ([SpecSysRead.sys_rw_count_lt]).

   NOTHING ABOUT THE BITMAP CROSSES EITHER WAY.  The block bitmap is a
   persistent invariant ([BitmapInv.bitmap_inv], carried inside
   [filewrite_fs_env]), so [write_env_frame]'s wand answers
   [filewrite_fs_out fn] flat -- no set, no existential, and no witness for
   this shell to pick on the three arms that never reach the allocator. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved KernelText.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import IntrDefs HartTp WpNext WpLock.
Require Import ProcGeom CpuOwn.
Require Import FdSlots ProcInv.
Require Import ProofKforkParts.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import WpUart.
Require Import LogInv.
Require Import Xv6Cameras.          (* [fsCrashG] -- filewrite's extra class *)
Require Import IrefSlots.
(* [consolewrite_stack] -- the stack budget unfolds to it *)
Require Import SpecArgfd SpecArgint SpecArgaddr SpecFilewrite.
(* [Require Import] is NOT transitive for the Import half, so SpecSysRead has
   to be named here even though SpecSysWrite requires it: [sys_rw_count],
   [sys_rw_count_reg] and [sys_rw_count_lt] all live there. *)
Require Import SpecSysRead.
Require Import SpecSysWrite.
Require Import CodeSysWrite.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.

(* a failing tactic in a whole-function WP over [proc_priv] otherwise spends
   tens of minutes formatting the goal (durable-notes) *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  Pure arithmetic: the frame and the three local addresses.             *)
(* ===================================================================== *)

(* the record-eta step: nothing on the -1 path touches the page table *)
Lemma sw_upd_upt_id (V : pprivate) : upd_upt V (pv_upt V) = V.
Proof. destruct V; reflexivity. Qed.

(* [addi a1,s0,-40] / [ld a1,-40(s0)] : &p, the whole of frame slot 5 *)
Lemma sw_addr_p (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 0xfd8 : mword 12)) = pa_stk X 5.
Proof.
  unfold pa_stk, add_vec_int. apply f_equal.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* [addi a1,s0,-28] / [lw a2,-28(s0)] : &n, the UPPER WORD of frame slot 4 *)
Lemma sw_addr_n (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 0xfe4 : mword 12)) = pa_add (pa_stk X 4) 4.
Proof.
  unfold pa_add, pa_stk, add_vec_int. rewrite pa_stk_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

(* [addi a2,s0,-24] / [ld a0,-24(s0)] : &f, the whole of frame slot 3 *)
Lemma sw_addr_f (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 0xfe8 : mword 12)) = pa_stk X 3.
Proof.
  unfold pa_stk, add_vec_int. apply f_equal.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* ...and slot 3 is 24 bytes above the frame base, the form the non-null
   argument needs ([StackOwn.stack_off_nonzero] is anchored at sp). *)
Lemma sw_addr_f_base (X : mword 64) :
  pa_stk X 3 = add_vec_int (pa_stk X 6) 24.
Proof. unfold pa_stk. rewrite avi_assoc. f_equal; lia. Qed.

Module SysWriteProof (Argaddr : ARGADDR) (Argint : ARGINT) (Argfd : ARGFD)
                    (Filewrite : FILEWRITE) : SYSWRITE.

Section ProofSysWrite.
  (* NO [!icacheG Σ]: [fileG] bundles it (SpecFilewrite.v's note). *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
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
     [ProofSysFstat.sfs_sp_bounds] verbatim. *)
  Lemma sw_sp_bounds `{CID0 : CpuId} (mm : regfile) (kk : nat)
      (bb : bool) (pp : mword 64) :
    (0 < kk)%nat ->
    sie_cap_gpr KT1 mm kk bb pp -∗
    ⌜(8 <= uint (mm !!! Regidx csp_rs1) < 274877906944 + 8)%Z⌝.
  Proof.
    iIntros (Hk) "(_ & _ & (Hstk & _ & _) & _)".
    iApply (stack_own_sp_bounds (KTR := KT1) _ (trap_res bb + kk)%nat with "Hstk").
    destruct bb; unfold trap_res; lia.
  Qed.

  (* =================================================================== *)
  (*  The shared tail at +0x40: the epilogue, over whatever is in a0.     *)
  (* =================================================================== *)
  (* A DECOMPOSED helper (porting guide): its own fresh [CID0] binder -- it
     is entered at a MIGRATED hart -- its own [b] and [pp], and its
     continuation wrapped in [wp_next].  It does NOT carry [cpu_own]: the
     epilogue never touches it, so the caller transports it afterwards. *)
  Lemma sw_tail `{CID0 : CpuId}
      (m Mt : regfile) (av : nat) (rv : mword 64)
      (sp0 ra0 s00 : mword 64) (w3 w4 w5 w6 : bv 64) (b : bool) (pp : mword 64) :
    (6 <= av)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 6 ->
    Mt !!! Regidx Ra0 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr KT1 Mt (av - 6)%nat b pp -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.sys_write + 0x40) : mword 64) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) w3 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) w4 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) w6 -∗
    wp_next (CID0 := CID0) b pp (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr KT1 mf av b pp -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Hsp0 Hra0 Hs00 Hmtsp Hmta0 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hcont".
    (* ---- +0x40: c.ldsp ra,40(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hmtsp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_write + 0x40))
              (mword_of_int 5 : mword 6) Rra Mt (av - 6)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb1").
    { iApply (swri_40 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    change (<[Regidx Rra := regval_into_reg ra0]> Mt) with T1.
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x40) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_write + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T1 upd_ne; [exact Hmtsp | reg_neq]).
    (* ---- +0x42: c.ldsp s0,32(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_write + 0x42))
              (mword_of_int 4 : mword 6) Rs0 T1 (av - 6)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb2").
    { iApply (swri_42 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x42) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_write + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x44: c.addi16sp sp,48 (frame pop) ---- *)
    assert (Hwv : add_vec (T2 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0)
      by (rewrite HT2sp; apply stk_pop_48).
    assert (Hpop : T2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T2 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6)
      by (rewrite Hwv; exact HT2sp).
    (* NO [stack_own_6_elim]/[_intro] exists: ProofSysPipe's slot recipe is
       what rebundles a frame of any width. *)
    iAssert (stack_own (KTR := KT1) sp0 6) with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6]" as "Hframe".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hb1"; [iExists _; iExact "Hb1"|].
      iSplitL "Hb2"; [iExists _; iExact "Hb2"|].
      iSplitL "Hb3"; [iExists _; iExact "Hb3"|].
      iSplitL "Hb4"; [iExists _; iExact "Hb4"|].
      iSplitL "Hb5"; [iExists _; iExact "Hb5"|].
      iSplitL "Hb6"; [iExists _; iExact "Hb6"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.sys_write + 0x44))
              (mword_of_int 3 : mword 6) T2 (av - 6)%nat 6 b Hpop
              with "Hcg Hpc [] Hframe").
    { iApply (swri_44 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc".
    assert (Hnk : ((av - 6) + 6)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x44) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_write + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp46) in "Hpc".
    set (T3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (T2 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T2).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (T2 !!! Regidx csp_rs1)
              (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T2) with T3.
    (* ---- +0x46: c.ret ---- *)
    assert (HT3ra : T3 !!! Regidx Rra = ra0).
    { rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.sys_write + 0x46))
              Rra T3 av b ltac:(vm_compute; discriminate)
              with "Hcg Hpc []").
    { iApply (swri_46 with "Htext"). }
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
  Lemma wp_sys_write_sconf
      (γa γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (fn : fwrite_names) (pidv : mword 32) (V : pprivate) (v v2 : mword 64)
      (m : regfile) (av : nat) (eb : bool) (b : bool) (lks : gset string)
    : wp_sys_write_sconf_body γa γf γs j γlp fn pidv V v v2 m av eb b lks.
  Proof.
    cbv beta delta [wp_sys_write_sconf_body].
    intros pcE pj ret_tgt Hav Hj Hgs Hlens Hfj Hfprocs
           Harg0 Harg1 Harg2 Hwp Hdq Heb.
    (* every budget, or [lia] cannot see past [filewrite_stack] -- it is an
       expression, not a literal, on purpose (SpecSysWrite.v). *)
    
    (* BOTH HALVES ARE FREE: the count is a [bv_signed] of a 32-bit cell, so
       it is an [int] and nothing has to be assumed about it
       ([SpecSysRead.sys_rw_count_range]).  Hoisted to a NAMED fact rather
       than written as an inline [ltac:] in argument position --
       durable-notes' divergence trap. *)
    assert (Hnrange : - 2 ^ 31 <= sys_rw_count v2 < 2 ^ 31)
      by apply sys_rw_count_range.
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
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    (* [KvmSpec.kalloc_env γa None] IS PERSISTENT (durable-notes.md): filewrite
       consumes it and does not give it back, and this contract's post owes it
       -- so it must be introduced with [#], not threaded. *)
    iIntros "Hcg Hcpu #Htext #Hdata Hpc #Hpenv Hpriv #Hkenv #Hprocs Henv #Hcaps #Htbl Hcont".
    (* THE DEVICE COLUMN, PROJECTED out of the console table.  The CAPS are
       separate -- consolewrite drives the UART, so they are [dev_inv] and
       the tx lock, both from [printk_env] -- and both halves are persistent,
       so nothing has to come back. *)
    iPoseProof (filewrite_devsw_of_console fn Hwp Hdq with "Hcaps Htbl") as "#Hdev".
    (* depth 0 forces the held set empty, so this body needs no order
       premise of its own -- every [locks_below] its callees raise is
       [locks_below ∅ _], which [lkbelow] closes outright. *)
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlkempty Hcpu]".
    (* PIN THE INDEX.  [eb = true] plus [cpu_own_eb_agree] at level 0 makes
       [b] the literal [true], which is what lets argaddr's, argint's and
       argfd's [wp_next b] crossings meet filewrite's and this contract's
       [wp_next true]. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb).
    (* ---- +0x00: c.addi16sp sp,-48 (frame push) ---- *)
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m av 6 b
              ltac:(lia) (stk_push_48 (m !!! Regidx csp_rs1))
              with "Hcg Hpc []").
    { iApply (swri_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.sys_write + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /M1 upd_eq; apply stk_push_48).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(P1 & P2 & P3 & P4 & P5 & P6 & _)".
    iDestruct "P1" as (u1) "Hs1". iDestruct "P2" as (u2) "Hs2".
    iDestruct "P3" as (w3) "Hs3". iDestruct "P4" as (w4) "Hs4".
    iDestruct "P5" as (w5) "Hs5". iDestruct "P6" as (w6) "Hs6".
    (* ---- +0x02: c.sdsp ra,40(sp) ---- *)
    assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hs1".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_write + 0x02))
              (mword_of_int 5 : mword 6) Rra M1 (av - 6)%nat u1 b
              with "Hcg Hpc [] Hs1").
    { iApply (swri_02 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc Hs1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_write + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- +0x04: c.sdsp s0,32(sp) ---- *)
    iEval (rewrite -Hpa2) in "Hs2".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_write + 0x04))
              (mword_of_int 4 : mword 6) Rs0 M1 (av - 6)%nat u2 b
              with "Hcg Hpc [] Hs2").
    { iApply (swri_04 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc Hs2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_write + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    assert (HM1ra : forall CID' : CpuId, rget (CID := CID') M1 Rra = ra0).
    { intros CID'; rgne. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    assert (HM1s0 : forall CID' : CpuId, rget (CID := CID') M1 Rs0 = s00).
    { intros CID'; rgne. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite Hpa1 HM1ra) in "Hs1".
    iEval (rewrite Hpa2 HM1s0) in "Hs2".
    (* ---- +0x06: c.addi4spn s0,sp,48 -- s0 := the entry sp ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.sys_write + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) Rs0
              M1 (av - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (swri_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1).
    change (<[Regidx Rs0 := regval_into_reg
              (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1) with M2.
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_write + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    assert (HM2s0 : M2 !!! Regidx Rs0 = sp0).
    { rewrite /M2 upd_eq HM1sp. apply stk_fp_48. }
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /M2 upd_ne; [exact HM1sp | reg_neq]).
    (* THE [int n] IS THE UPPER HALF OF SLOT 4: carve it now, take the
       8-alignment fact out FIRST (the halves no longer carry it). *)
    iDestruct (word_pointsto_aligned_p with "Hs4") as %Hal4.
    iDestruct (word_pointsto_split4 with "Hs4") as "[Hs4lo Hs4hi]".
    (* ---- +0x08: addi a1,s0,-40 -- a1 := &p ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_write + 0x08))
              Ra1 Rs0 (mword_of_int 0xfd8 : mword 12) M2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (swri_08 with "Htext"). }
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (M3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget M2 Rs0) (sign_extend' 64 (mword_of_int 0xfd8 : mword 12)))]> M2).
    change (<[Regidx Ra1 := regval_into_reg
              (add_vec (rget M2 Rs0) (sign_extend' 64 (mword_of_int 0xfd8 : mword 12)))]> M2) with M3.
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x08) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_write + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    assert (HM3a1 : M3 !!! Regidx Ra1 = pa_stk sp0 5).
    { rewrite /M3 upd_eq. rgne. rewrite HM2s0. apply sw_addr_p. }
    assert (HM3s0 : M3 !!! Regidx Rs0 = sp0)
      by (rewrite /M3 upd_ne; [exact HM2s0 | reg_neq]).
    assert (HM3sp : M3 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /M3 upd_ne; [exact HM2sp | reg_neq]).
    (* ---- +0x0c: c.li a0,1 -- the argument index ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_write + 0x0c))
              Ra0 (mword_of_int 1 : mword 6)
              (mword_of_int (Z.of_nat 1) : mword 64) M3 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (swri_0c with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (M4 := <[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat 1) : mword 64)]> M3).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat 1) : mword 64)]> M3) with M4.
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_write + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* ---- +0x0e: jal ra,argaddr ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_write + 0x0e))
              Rra (mword_of_int 2087556 : mword 21) M4 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (swri_0e with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (M5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_write + 0x0e) : mword 64) 4)]> M4).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.sys_write + 0x0e) : mword 64) 4)]> M4) with M5.
    assert (Hjaa : add_vec (mword_of_int (KernelSyms.sys_write + 0x0e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2087556 : mword 21)) = mword_of_int KernelSyms.argaddr)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaa) in "Hpc".
    assert (HM5a0 : M5 !!! Regidx Ra0 = mword_of_int (Z.of_nat 1)).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_eq. reflexivity. }
    assert (HM5a1 : M5 !!! Regidx Ra1 = pa_stk sp0 5).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq]. exact HM3a1. }
    assert (HM5s0 : M5 !!! Regidx Rs0 = sp0).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq]. exact HM3s0. }
    assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq]. exact HM3sp. }
    assert (HM5ra : M5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.sys_write + 0x0e) : mword 64) 4)
      by (rewrite /M5 upd_eq; reflexivity).
    (* argaddr wants the trapframe pointer fraction and the page, out of the
       block; the wand puts both back the instant it returns. *)
    iDestruct (proc_priv_tfp_valid with "Hpriv") as %Hpv.
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpback)".
    iEval (rewrite -HM5a1) in "Hs5".
    iDestruct (cpu_own_transport CID CID7 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Argaddr.wp_argaddr_sconf M5 (av - 6)%nat 0%nat eb pj 1%nat
              (ud_tfp (pv_upt V)) (pv_tf V) v1 w5 (DfracOwn (1/4)) b lks
              ltac:(unfold NARG; lia) HM5a0 Harg1 Hnoff
              ltac:(lia) Hpv
              with "Hcg Hcpu Htext Hdata Hpc Htfc Htfp Hs5").
    iIntros (CID8 Hs8 A0) "%HcsA0 Hcg Hcpu Hpc Htfc Htfp Hs5".
    iEval (rewrite HM5a1) in "Hs5".
    iDestruct ("Hpback" with "Htfc Htfp") as "Hpriv".
    assert (Hpc12 : ret_pc (M5 !!! Regidx Rra)
                    = mword_of_int (KernelSyms.sys_write + 0x12))
      by (rewrite HM5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    assert (HA0s0 : A0 !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsA0 Rs0 ltac:(vm_compute; reflexivity)); exact HM5s0).
    assert (HA0sp : A0 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup HcsA0 csp_rs1 ltac:(vm_compute; reflexivity)); exact HM5sp).
    (* ---- +0x12: addi a1,s0,-28 -- a1 := &n (the UPPER half of slot 4) ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_write + 0x12))
              Ra1 Rs0 (mword_of_int 0xfe4 : mword 12) A0 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (swri_12 with "Htext"). }
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (B1 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget A0 Rs0) (sign_extend' 64 (mword_of_int 0xfe4 : mword 12)))]> A0).
    change (<[Regidx Ra1 := regval_into_reg
              (add_vec (rget A0 Rs0) (sign_extend' 64 (mword_of_int 0xfe4 : mword 12)))]> A0) with B1.
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x12) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_write + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    assert (HB1a1 : B1 !!! Regidx Ra1 = pa_add (pa_stk sp0 4) 4).
    { rewrite /B1 upd_eq. rgne. rewrite HA0s0. apply sw_addr_n. }
    assert (HB1s0 : B1 !!! Regidx Rs0 = sp0)
      by (rewrite /B1 upd_ne; [exact HA0s0 | reg_neq]).
    assert (HB1sp : B1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /B1 upd_ne; [exact HA0sp | reg_neq]).
    (* ---- +0x16: c.li a0,2 -- the argument index ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_write + 0x16))
              Ra0 (mword_of_int 2 : mword 6)
              (mword_of_int (Z.of_nat 2) : mword 64) B1 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (swri_16 with "Htext"). }
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (B2 := <[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat 2) : mword 64)]> B1).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat 2) : mword 64)]> B1) with B2.
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x16) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_write + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* ---- +0x18: jal ra,argint ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_write + 0x18))
              Rra (mword_of_int 2087518 : mword 21) B2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (swri_18 with "Htext"). }
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (B3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_write + 0x18) : mword 64) 4)]> B2).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.sys_write + 0x18) : mword 64) 4)]> B2) with B3.
    assert (Hjai : add_vec (mword_of_int (KernelSyms.sys_write + 0x18) : mword 64)
                     (sign_extend' 64 (mword_of_int 2087518 : mword 21)) = mword_of_int KernelSyms.argint)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjai) in "Hpc".
    assert (HB3a0 : B3 !!! Regidx Ra0 = mword_of_int (Z.of_nat 2)).
    { rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_eq. reflexivity. }
    assert (HB3a1 : B3 !!! Regidx Ra1 = pa_add (pa_stk sp0 4) 4).
    { rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq]. exact HB1a1. }
    assert (HB3s0 : B3 !!! Regidx Rs0 = sp0).
    { rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq]. exact HB1s0. }
    assert (HB3sp : B3 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq]. exact HB1sp. }
    assert (HB3ra : B3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.sys_write + 0x18) : mword 64) 4)
      by (rewrite /B3 upd_eq; reflexivity).
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpback)".
    iDestruct (cpu_own_transport CID8 CID11 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Argint.wp_argint_sconf B3 (av - 6)%nat 0%nat eb pj 2%nat
              (ud_tfp (pv_upt V)) (pv_tf V) v2 (word_hi w4) (DfracOwn (1/4)) b lks
              ltac:(unfold NARG; lia) HB3a0 Harg2 Hnoff ltac:(lia) Hpv
              with "Hcg Hcpu Htext Hdata Hpc Htfc Htfp [Hs4hi]").
    { iEval (rewrite HB3a1). iExact "Hs4hi". }
    iIntros (CID12 Hs12 A1) "%HcsA1 Hcg Hcpu Hpc Htfc Htfp Hs4hi".
    iEval (rewrite HB3a1) in "Hs4hi".
    iDestruct ("Hpback" with "Htfc Htfp") as "Hpriv".
    assert (Hpc1c : ret_pc (B3 !!! Regidx Rra)
                    = mword_of_int (KernelSyms.sys_write + 0x1c))
      by (rewrite HB3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    assert (HA1s0 : A1 !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsA1 Rs0 ltac:(vm_compute; reflexivity)); exact HB3s0).
    assert (HA1sp : A1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup HcsA1 csp_rs1 ltac:(vm_compute; reflexivity)); exact HB3sp).
    (* ---- +0x1c: addi a2,s0,-24 -- a2 := &f ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_write + 0x1c))
              Ra2 Rs0 (mword_of_int 0xfe8 : mword 12) A1 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (swri_1c with "Htext"). }
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (N1 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (rget A1 Rs0) (sign_extend' 64 (mword_of_int 0xfe8 : mword 12)))]> A1).
    change (<[Regidx Ra2 := regval_into_reg
              (add_vec (rget A1 Rs0) (sign_extend' 64 (mword_of_int 0xfe8 : mword 12)))]> A1) with N1.
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x1c) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_write + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    assert (HN1a2 : N1 !!! Regidx Ra2 = pa_stk sp0 3).
    { rewrite /N1 upd_eq. rgne. rewrite HA1s0. apply sw_addr_f. }
    assert (HN1s0 : N1 !!! Regidx Rs0 = sp0)
      by (rewrite /N1 upd_ne; [exact HA1s0 | reg_neq]).
    assert (HN1sp : N1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /N1 upd_ne; [exact HA1sp | reg_neq]).
    (* ---- +0x20: c.li a1,0 -- pfd = NULL ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_write + 0x20))
              Ra1 (mword_of_int 0 : mword 6) (zero_reg : mword 64) N1 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (swri_20 with "Htext"). }
    iIntros (CID14 Hs14) "Hcg Hpc".
    set (N2 := <[Regidx Ra1 := regval_into_reg (zero_reg : mword 64)]> N1).
    change (<[Regidx Ra1 := regval_into_reg (zero_reg : mword 64)]> N1) with N2.
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_write + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* ---- +0x22: c.li a0,0 -- the argument index ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_write + 0x22))
              Ra0 (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0) : mword 64) N2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (swri_22 with "Htext"). }
    iIntros (CID15 Hs15) "Hcg Hpc".
    set (N3 := <[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat 0) : mword 64)]> N2).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat 0) : mword 64)]> N2) with N3.
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_write + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* ---- +0x24: jal ra,argfd ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_write + 0x24))
              Rra (mword_of_int 2096458 : mword 21) N3 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (swri_24 with "Htext"). }
    iIntros (CID16 Hs16) "Hcg Hpc".
    set (N4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_write + 0x24) : mword 64) 4)]> N3).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.sys_write + 0x24) : mword 64) 4)]> N3) with N4.
    assert (Hjafd : add_vec (mword_of_int (KernelSyms.sys_write + 0x24) : mword 64)
                      (sign_extend' 64 (mword_of_int 2096458 : mword 21)) = mword_of_int KernelSyms.argfd)
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
    assert (HN4sp : N4 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_ne; [| reg_neq]. exact HN1sp. }
    assert (HN4ra : N4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.sys_write + 0x24) : mword 64) 4)
      by (rewrite /N4 upd_eq; reflexivity).
    (* [pf] is not null: the frame's own geometry, no assumption about where
       the kernel stack lives. *)
    assert (Hkpos : (0 < (av - 6)%nat)%nat) by lia.
    iDestruct (sw_sp_bounds _ _ _ _ Hkpos with "Hcg") as %Hspb.
    rewrite HN4sp in Hspb.
    assert (Hnzf : N4 !!! Regidx Ra2 <> (zero_reg : mword 64)).
    { rewrite HN4a2 sw_addr_f_base. apply stack_off_nonzero; [exact Hspb | lia]. }
    iEval (rewrite -HN4a2) in "Hs3".
    iDestruct (cpu_own_transport CID12 CID16 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                 with "Hcpu") as "Hcpu".
    (* ---- argfd(0, 0, &f).  [pfd] IS NULL and carries no resource --
       [SpecArgfd.ofd_out_null] is exactly this case. ---- *)
    iApply (Argfd.wp_argfd_sconf γf N4 (av - 6)%nat 0%nat eb pj 0%nat v
              pidv V (bv_0 32) w3 b lks
              ltac:(unfold NARG; lia) HN4a0 Harg0 Hnzf Hnoff
              ltac:(lia)
              with "Hcg Hcpu Htext Hdata Hpc Hpriv [] Hs3").
    { iApply (ofd_out_null _ _ HN4a1). }
    iIntros (CID17 Hs17 A) "%HcsA Hcg Hcpu Hpc Hpriv Hpost".
    assert (Hpc28 : ret_pc (N4 !!! Regidx Rra)
                    = mword_of_int (KernelSyms.sys_write + 0x28))
      by (rewrite HN4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* ---- +0x28: c.mv a5,a0 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_write + 0x28))
              Ra5 Ra0 A (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (swri_28 with "Htext"). }
    iIntros (CID18 Hs18) "Hcg Hpc".
    set (A2 := <[Regidx Ra5 := regval_into_reg (add_vec zero_reg (rget A Ra0))]> A).
    change (<[Regidx Ra5 := regval_into_reg (add_vec zero_reg (rget A Ra0))]> A) with A2.
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x28) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_write + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    assert (HA2a5 : A2 !!! Regidx Ra5 = A !!! Regidx Ra0).
    { rewrite /A2 upd_eq. rgne. apply add_vec_zero_l. }
    (* ---- +0x2a: c.li a0,-1 (the error return, HOISTED above the branch) ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_write + 0x2a))
              Ra0 (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) A2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (swri_2a with "Htext"). }
    iIntros (CID19 Hs19) "Hcg Hpc".
    set (A3 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> A2).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> A2) with A3.
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x2a) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_write + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    assert (HA3a0 : A3 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
      by (rewrite /A3 upd_eq; reflexivity).
    assert (HA3a5 : A3 !!! Regidx Ra5 = A !!! Regidx Ra0)
      by (rewrite /A3 upd_ne; [exact HA2a5 | reg_neq]).
    assert (HA3sp : A3 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)). exact HN4sp. }
    assert (HA3s0 : A3 !!! Regidx Rs0 = sp0).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsA Rs0 ltac:(vm_compute; reflexivity)). exact HN4s0. }
    (* the residual threading fact both arms hand on *)
    assert (HthrA : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> A3 !!! Regidx r = m !!! Regidx r).
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
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsA r Hr).
      rewrite /N4 upd_ne; [| congruence].
      rewrite /N3 upd_ne; [| congruence].
      rewrite /N2 upd_ne; [| congruence].
      rewrite /N1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsA1 r Hr).
      rewrite /B3 upd_ne; [| congruence].
      rewrite /B2 upd_ne; [| congruence].
      rewrite /B1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsA0 r Hr).
      rewrite /M5 upd_ne; [| congruence].
      rewrite /M4 upd_ne; [| congruence].
      rewrite /M3 upd_ne; [| congruence].
      rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    (* ---- +0x2c: blt a5,x0 -- the two arms ---- *)
    rewrite /argfd_post. iDestruct "Hpost" as "[Hfail | Hsucc]".
    - (* ================= FAILURE: argfd returned -1 ================= *)
      iDestruct "Hfail" as "([%Hr %Hnone] & _ & Hfcell)".
      assert (HA3a5' : A3 !!! Regidx Ra5 = (mword_of_int (-1) : mword 64))
        by (rewrite HA3a5; exact Hr).
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.sys_write + 0x2c))
                (mword_of_int 20 : mword 13) Ra5 A3 (av - 6)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HA3a5'; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (swri_2c with "Htext"). }
      iNext. iIntros (CID20 Hs20) "Hcg Hpc".
      assert (Htgt40 : add_vec (mword_of_int (KernelSyms.sys_write + 0x2c) : mword 64)
                (sign_extend' 64 (mword_of_int 20 : mword 13))
                = mword_of_int (KernelSyms.sys_write + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt40) in "Hpc".
      iEval (rewrite HN4a2) in "Hfcell".
      (* slot 4 goes back together: both halves are dead from here on *)
      iDestruct (word_pointsto_join4 _ _ _ _ Hal4 with "Hs4lo Hs4hi") as "Hs4".
      iApply (sw_tail (CID0 := CID20) m A3 av (mword_of_int (-1) : mword 64)
                sp0 ra0 s00 _ _ _ _ b pj
                ltac:(lia) eq_refl eq_refl eq_refl HA3sp HA3a0 HthrA
                with "Hcg Htext Hpc Hs1 Hs2 Hfcell Hs4 Hs5 Hs6").
      iIntros (CID21 Hs21 mf) "[%Hcsf %Hmfa0] Hcg Hpc".
     iDestruct (cpu_own_transport CID17 CID21 0%nat eb pj b 
                   ltac:(rewrite Hb; wp_next_chain) with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CID21 with "[%]"); [wp_next_chain|].
      (* nothing ran, so the page table is its own extension *)
      iApply ("Hcont" $! mf (mword_of_int (-1) : mword 64) (pv_upt V)
                with "[%] [%] [%] [%] Hcg Hcpu Hpc [Hpriv] Hkenv [Henv]").
      { exact Hcsf. }
      { apply uptd_ext_refl. }
      { left. split; [reflexivity | exact Hnone]. }
      { exact Hmfa0. }
      { rewrite sw_upd_upt_id. iExact "Hpriv". }
      { iApply (filewrite_fs_env_out with "Henv"). }
    - (* ================= SUCCESS: the descriptor resolved ============= *)
      iDestruct "Hsucc" as (fd fv) "([%Hr %Hsome] & _ & Hfcell)".
      pose proof (arg_fd_lookup v (pv_ofile V) fd fv Hsome)
        as (Hfdlt & Hlk & Hfvnz & _).
      assert (HA3a5' : A3 !!! Regidx Ra5 = (zero_reg : mword 64))
        by (rewrite HA3a5; exact Hr).
      iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.sys_write + 0x2c))
                (mword_of_int 20 : mword 13) Ra5 A3 (av - 6)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HA3a5'; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (swri_2c with "Htext"). }
      iIntros (CID20 Hs20) "Hcg Hpc".
      assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x2c) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_write + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp30) in "Hpc".
      (* ---- +0x30: lw a2,-28(s0) -- the count, SIGN-extended ---- *)
      assert (Haddrn : forall CID' : CpuId,
                add_vec (rget (CID := CID') A3 Rs0)
                        (sign_extend' 64 (mword_of_int 0xfe4 : mword 12))
                = pa_add (pa_stk sp0 4) 4).
      { intros CID'; rgne. rewrite HA3s0. apply sw_addr_n. }
      iEval (rewrite -(Haddrn CID20)) in "Hs4hi".
      iApply (wp_lw_s_sconf (CID := CID20) (mword_of_int (KernelSyms.sys_write + 0x30))
                Ra2 Rs0 (mword_of_int 0xfe4 : mword 12) A3 (av - 6)%nat (arg_int32 v2) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hs4hi").
      { iApply (swri_30 with "Htext"). }
      iIntros (CID21 Hs21) "Hcg Hpc Hs4hi".
      iEval (rewrite (Haddrn CID20)) in "Hs4hi".
      set (S1 := <[Regidx Ra2 := regval_into_reg
                    (sign_extend' 64 (arg_int32 v2))]> A3).
      change (<[Regidx Ra2 := regval_into_reg
                (sign_extend' 64 (arg_int32 v2))]> A3) with S1.
      assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x30) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_write + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp34) in "Hpc".
      assert (HS1a2 : S1 !!! Regidx Ra2 = (mword_of_int (sys_rw_count v2) : mword 64)).
      { rewrite /S1 upd_eq. apply sys_rw_count_reg. }
      assert (HS1s0 : S1 !!! Regidx Rs0 = sp0)
        by (rewrite /S1 upd_ne; [exact HA3s0 | reg_neq]).
      assert (HS1sp : S1 !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /S1 upd_ne; [exact HA3sp | reg_neq]).
      (* ---- +0x34: ld a1,-40(s0) -- reload p ---- *)
      assert (Haddrp : forall CID' : CpuId,
                add_vec (rget (CID := CID') S1 Rs0)
                        (sign_extend' 64 (mword_of_int 0xfd8 : mword 12)) = pa_stk sp0 5).
      { intros CID'; rgne. rewrite HS1s0. apply sw_addr_p. }
      iEval (rewrite -(Haddrp CID21)) in "Hs5".
      iApply (wp_ld_s_sconf (CID := CID21) (mword_of_int (KernelSyms.sys_write + 0x34))
                Ra1 Rs0 (mword_of_int 0xfd8 : mword 12) S1 (av - 6)%nat v1 b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hs5").
      { iApply (swri_34 with "Htext"). }
      iIntros (CID22 Hs22) "Hcg Hpc Hs5".
      iEval (rewrite (Haddrp CID21)) in "Hs5".
      set (S2 := <[Regidx Ra1 := regval_into_reg v1]> S1).
      change (<[Regidx Ra1 := regval_into_reg v1]> S1) with S2.
      assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x34) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_write + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      assert (HS2a2 : S2 !!! Regidx Ra2 = (mword_of_int (sys_rw_count v2) : mword 64))
        by (rewrite /S2 upd_ne; [exact HS1a2 | reg_neq]).
      assert (HS2s0 : S2 !!! Regidx Rs0 = sp0)
        by (rewrite /S2 upd_ne; [exact HS1s0 | reg_neq]).
      assert (HS2sp : S2 !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /S2 upd_ne; [exact HS1sp | reg_neq]).
      (* ---- +0x38: ld a0,-24(s0) -- reload f ---- *)
      assert (Haddrf : forall CID' : CpuId,
                add_vec (rget (CID := CID') S2 Rs0)
                        (sign_extend' 64 (mword_of_int 0xfe8 : mword 12)) = pa_stk sp0 3).
      { intros CID'; rgne. rewrite HS2s0. apply sw_addr_f. }
      iEval (rewrite HN4a2) in "Hfcell".
      iEval (rewrite -(Haddrf CID22)) in "Hfcell".
      iApply (wp_ld_s_sconf (CID := CID22) (mword_of_int (KernelSyms.sys_write + 0x38))
                Ra0 Rs0 (mword_of_int 0xfe8 : mword 12) S2 (av - 6)%nat fv b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hfcell").
      { iApply (swri_38 with "Htext"). }
      iIntros (CID23 Hs23) "Hcg Hpc Hfcell".
      iEval (rewrite (Haddrf CID22)) in "Hfcell".
      set (S3 := <[Regidx Ra0 := regval_into_reg fv]> S2).
      change (<[Regidx Ra0 := regval_into_reg fv]> S2) with S3.
      assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.sys_write + 0x38) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_write + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      assert (HS3a2 : S3 !!! Regidx Ra2 = (mword_of_int (sys_rw_count v2) : mword 64))
        by (rewrite /S3 upd_ne; [exact HS2a2 | reg_neq]).
      assert (HS3s0 : S3 !!! Regidx Rs0 = sp0)
        by (rewrite /S3 upd_ne; [exact HS2s0 | reg_neq]).
      assert (HS3sp : S3 !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /S3 upd_ne; [exact HS2sp | reg_neq]).
      (* ---- +0x3c: jal ra,filewrite ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_write + 0x3c))
                Rra (mword_of_int 2094382 : mword 21) S3 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (swri_3c with "Htext"). }
      iIntros (CID24 Hs24) "Hcg Hpc".
      set (S4 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.sys_write + 0x3c) : mword 64) 4)]> S3).
      change (<[Regidx Rra := regval_into_reg
                (add_vec_int (mword_of_int (KernelSyms.sys_write + 0x3c) : mword 64) 4)]> S3) with S4.
      assert (Hjfr : add_vec (mword_of_int (KernelSyms.sys_write + 0x3c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094382 : mword 21)) = mword_of_int KernelSyms.filewrite)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjfr) in "Hpc".
      assert (HS4ra : S4 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.sys_write + 0x3c) : mword 64) 4)
        by (rewrite /S4 upd_eq; reflexivity).
      assert (HS4a0 : S4 !!! Regidx Ra0 = fv).
      { rewrite /S4 upd_ne; [| reg_neq]. rewrite /S3 upd_eq. reflexivity. }
      assert (HS4a2 : S4 !!! Regidx Ra2 = (mword_of_int (sys_rw_count v2) : mword 64))
        by (rewrite /S4 upd_ne; [exact HS3a2 | reg_neq]).
      assert (HS4sp : S4 !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /S4 upd_ne; [exact HS3sp | reg_neq]).
      (* ---- THE B1 SEAM.  Lend the descriptor's reference out of the block,
         keep the core for filewrite, and settle the loan when it returns. ---- *)
      iDestruct (proc_priv_lend γf pj pidv V fd fv Hlk Hfvnz with "Hpriv")
        as (kk qq Cf) "([%Hfvk %Hkk] & Href & Hcore & Howe)".
      assert (HS4a0' : S4 !!! Regidx Ra0 = fnode kk) by (rewrite HS4a0; exact Hfvk).
      iDestruct (write_env_frame γf fn Cf with "Henv Hdev") as "[Hfenv Hfback]".
      iDestruct (cpu_own_transport CID17 CID24 0%nat eb pj b 
                   ltac:(rewrite Hb; wp_next_chain) with "Hcpu") as "Hcpu".
      iApply (Filewrite.wp_filewrite_sconf γa γf γs j γlp kk qq Cf fn pidv V
                S4 (av - 6)%nat eb (sys_rw_count v2) b lks
                ltac:(lia) Hkk Hj Hgs Hlens
                Hfj Hfprocs HS4a0' HS4a2 Hnrange Heb
                with "Hcg Hcpu Htext Hdata Hpc Hpenv Href Hcore Hkenv Hprocs Hfenv").
      all: try lkbelow.
      iIntros (CID25 Hs25 mf rv P')
        "%Hcsf %Hupt %Hrvok %Hrva Hcg Hcpu Hpc Href Hcore Hfout".
      iDestruct ("Hfback" with "Hfout") as "[Henv _]".
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
      assert (Hpc40 : ret_pc (S4 !!! Regidx Rra)
                      = mword_of_int (KernelSyms.sys_write + 0x40))
        by (rewrite HS4ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc40) in "Hpc".
      assert (HMfsp : mf !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite (callee_saved_lookup Hcsf csp_rs1 ltac:(vm_compute; reflexivity)); exact HS4sp).
      assert (HthrF : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> mf !!! Regidx r = m !!! Regidx r).
      { intros r Hrcs Ncsp N8.
        assert (N1' : r <> mword_of_int 1)
          by (intro He; rewrite He in Hrcs; vm_compute in Hrcs; discriminate).
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hrcs; vm_compute in Hrcs; discriminate).
        assert (N11 : r <> mword_of_int 11)
          by (intro He; rewrite He in Hrcs; vm_compute in Hrcs; discriminate).
        assert (N12 : r <> mword_of_int 12)
          by (intro He; rewrite He in Hrcs; vm_compute in Hrcs; discriminate).
        rewrite (callee_saved_lookup Hcsf r Hrcs).
        rewrite /S4 upd_ne; [| congruence].
        rewrite /S3 upd_ne; [| congruence].
        rewrite /S2 upd_ne; [| congruence].
        rewrite /S1 upd_ne; [| congruence].
        apply HthrA; assumption. }
      iDestruct (word_pointsto_join4 _ _ _ _ Hal4 with "Hs4lo Hs4hi") as "Hs4".
      iApply (sw_tail (CID0 := CID25) m mf av rv sp0 ra0 s00 _ _ _ _ b pj
                ltac:(lia) eq_refl eq_refl eq_refl HMfsp Hrva HthrF
                with "Hcg Htext Hpc Hs1 Hs2 Hfcell Hs4 Hs5 Hs6").
      iIntros (CID26 Hs26 mg) "[%Hcsg %Hmga0] Hcg Hpc".
      iDestruct (cpu_own_transport CID25 CID26 0%nat eb pj b 
                   ltac:(rewrite Hb; wp_next_chain) with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CID26 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mg rv P'
                with "[%] [%] [%] [%] Hcg Hcpu Hpc Hpriv Hkenv Henv").
      { exact Hcsg. }
      { exact Hupt. }
      { right. exists fd, fv. split; [exact Hsome | exact Hrvok]. }
      { exact Hmga0. }
  Qed.

End ProofSysWrite.

End SysWriteProof.
